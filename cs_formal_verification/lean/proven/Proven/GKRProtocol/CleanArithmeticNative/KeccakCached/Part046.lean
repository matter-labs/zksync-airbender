module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part045
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

local instance generatedBatch46Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch46Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealWitnessBinding112 :
    NumericPolynomialChecks.encodeCombination native.witness112 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 112 [] := by kernel_rfl

theorem native.idealInputsBinding112 :
    CleanExpression.inputs native.expression112 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 112 [] := by kernel_rfl

theorem native.checked112 :
    equal (CleanExpression.polynomial native.placement native.expression112)
        (combination native.relations native.witness112) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression112 native.witness112
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    112 (by decide +kernel) native.idealCodeBinding112 native.idealRelationsBinding native.idealWitnessBinding112

theorem native.preserved112 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression112).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression112 native.placement native.relations native.witness112
    native.checked112 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression113 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨16⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨18⟩))))
    (Airbender.Expression.var ⟨65⟩)

noncomputable def native.witness113 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨145, by decide⟩)]

theorem native.idealCodeBinding113 :
    CleanIdealChecks.encode native.placement native.expression113 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 113 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding113 :
    NumericPolynomialChecks.encodeCombination native.witness113 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 113 [] := by kernel_rfl

theorem native.idealInputsBinding113 :
    CleanExpression.inputs native.expression113 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 113 [] := by kernel_rfl

theorem native.checked113 :
    equal (CleanExpression.polynomial native.placement native.expression113)
        (combination native.relations native.witness113) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression113 native.witness113
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    113 (by decide +kernel) native.idealCodeBinding113 native.idealRelationsBinding native.idealWitnessBinding113

theorem native.preserved113 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression113).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression113 native.placement native.relations native.witness113
    native.checked113 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression114 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨19⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨21⟩))))
    (Airbender.Expression.var ⟨65⟩)

noncomputable def native.witness114 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨146, by decide⟩)]

theorem native.idealCodeBinding114 :
    CleanIdealChecks.encode native.placement native.expression114 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 114 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding114 :
    NumericPolynomialChecks.encodeCombination native.witness114 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 114 [] := by kernel_rfl

theorem native.idealInputsBinding114 :
    CleanExpression.inputs native.expression114 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 114 [] := by kernel_rfl

theorem native.checked114 :
    equal (CleanExpression.polynomial native.placement native.expression114)
        (combination native.relations native.witness114) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression114 native.witness114
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    114 (by decide +kernel) native.idealCodeBinding114 native.idealRelationsBinding native.idealWitnessBinding114

theorem native.preserved114 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression114).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression114 native.placement native.relations native.witness114
    native.checked114 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression115 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨20⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨22⟩))))
    (Airbender.Expression.var ⟨65⟩)

noncomputable def native.witness115 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨147, by decide⟩)]

theorem native.idealCodeBinding115 :
    CleanIdealChecks.encode native.placement native.expression115 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 115 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding115 :
    NumericPolynomialChecks.encodeCombination native.witness115 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 115 [] := by kernel_rfl

theorem native.idealInputsBinding115 :
    CleanExpression.inputs native.expression115 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 115 [] := by kernel_rfl

theorem native.checked115 :
    equal (CleanExpression.polynomial native.placement native.expression115)
        (combination native.relations native.witness115) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression115 native.witness115
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    115 (by decide +kernel) native.idealCodeBinding115 native.idealRelationsBinding native.idealWitnessBinding115
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
