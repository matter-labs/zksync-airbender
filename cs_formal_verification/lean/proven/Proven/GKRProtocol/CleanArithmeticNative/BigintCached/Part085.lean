module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part084
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

local instance generatedBatch85Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch85Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding130 :
    CleanIdealChecks.encode native.placement native.expression130 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 130 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding130 :
    NumericPolynomialChecks.encodeCombination native.witness130 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 130 [] := by kernel_rfl

theorem native.idealInputsBinding130 :
    CleanExpression.inputs native.expression130 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 130 [] := by kernel_rfl

theorem native.checked130 :
    equal (CleanExpression.polynomial native.placement native.expression130)
        (combination native.relations native.witness130) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression130 native.witness130
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    130 (by decide +kernel) native.idealCodeBinding130 native.idealRelationsBinding native.idealWitnessBinding130

theorem native.preserved130 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression130).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression130 native.placement native.relations native.witness130
    native.checked130 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression131 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨263⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨263⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness131 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨172, by decide⟩)]

theorem native.idealCodeBinding131 :
    CleanIdealChecks.encode native.placement native.expression131 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 131 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding131 :
    NumericPolynomialChecks.encodeCombination native.witness131 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 131 [] := by kernel_rfl

theorem native.idealInputsBinding131 :
    CleanExpression.inputs native.expression131 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 131 [] := by kernel_rfl

theorem native.checked131 :
    equal (CleanExpression.polynomial native.placement native.expression131)
        (combination native.relations native.witness131) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression131 native.witness131
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    131 (by decide +kernel) native.idealCodeBinding131 native.idealRelationsBinding native.idealWitnessBinding131

theorem native.preserved131 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression131).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression131 native.placement native.relations native.witness131
    native.checked131 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression132 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨266⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨266⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness132 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨173, by decide⟩)]

theorem native.idealCodeBinding132 :
    CleanIdealChecks.encode native.placement native.expression132 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 132 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding132 :
    NumericPolynomialChecks.encodeCombination native.witness132 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 132 [] := by kernel_rfl

theorem native.idealInputsBinding132 :
    CleanExpression.inputs native.expression132 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 132 [] := by kernel_rfl

theorem native.checked132 :
    equal (CleanExpression.polynomial native.placement native.expression132)
        (combination native.relations native.witness132) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression132 native.witness132
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    132 (by decide +kernel) native.idealCodeBinding132 native.idealRelationsBinding native.idealWitnessBinding132

theorem native.preserved132 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression132).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression132 native.placement native.relations native.witness132
    native.checked132 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression133 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨269⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨269⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness133 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨174, by decide⟩)]

theorem native.idealCodeBinding133 :
    CleanIdealChecks.encode native.placement native.expression133 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 133 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding133 :
    NumericPolynomialChecks.encodeCombination native.witness133 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 133 [] := by kernel_rfl

theorem native.idealInputsBinding133 :
    CleanExpression.inputs native.expression133 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 133 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BigintCached
