module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part075
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

local instance generatedBatch76Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch76Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealWitnessBinding99 :
    NumericPolynomialChecks.encodeCombination native.witness99 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 99 [] := by kernel_rfl

theorem native.idealInputsBinding99 :
    CleanExpression.inputs native.expression99 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 99 [] := by kernel_rfl

theorem native.checked99 :
    equal (CleanExpression.polynomial native.placement native.expression99)
        (combination native.relations native.witness99) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression99 native.witness99
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked 99
    (by decide +kernel) native.idealCodeBinding99 native.idealRelationsBinding native.idealWitnessBinding99

theorem native.preserved99 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression99).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression99 native.placement native.relations native.witness99
    native.checked99 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression100 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨84⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨84⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness100 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨141, by decide⟩)]

theorem native.idealCodeBinding100 :
    CleanIdealChecks.encode native.placement native.expression100 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 100 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding100 :
    NumericPolynomialChecks.encodeCombination native.witness100 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 100 [] := by kernel_rfl

theorem native.idealInputsBinding100 :
    CleanExpression.inputs native.expression100 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 100 [] := by kernel_rfl

theorem native.checked100 :
    equal (CleanExpression.polynomial native.placement native.expression100)
        (combination native.relations native.witness100) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression100 native.witness100
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    100 (by decide +kernel) native.idealCodeBinding100 native.idealRelationsBinding native.idealWitnessBinding100

theorem native.preserved100 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression100).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression100 native.placement native.relations native.witness100
    native.checked100 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression101 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨85⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨85⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness101 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨142, by decide⟩)]

theorem native.idealCodeBinding101 :
    CleanIdealChecks.encode native.placement native.expression101 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 101 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding101 :
    NumericPolynomialChecks.encodeCombination native.witness101 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 101 [] := by kernel_rfl

theorem native.idealInputsBinding101 :
    CleanExpression.inputs native.expression101 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 101 [] := by kernel_rfl

theorem native.checked101 :
    equal (CleanExpression.polynomial native.placement native.expression101)
        (combination native.relations native.witness101) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression101 native.witness101
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    101 (by decide +kernel) native.idealCodeBinding101 native.idealRelationsBinding native.idealWitnessBinding101

theorem native.preserved101 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression101).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression101 native.placement native.relations native.witness101
    native.checked101 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression102 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨86⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨86⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness102 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨143, by decide⟩)]

theorem native.idealCodeBinding102 :
    CleanIdealChecks.encode native.placement native.expression102 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 102 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding102 :
    NumericPolynomialChecks.encodeCombination native.witness102 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 102 [] := by kernel_rfl

theorem native.idealInputsBinding102 :
    CleanExpression.inputs native.expression102 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 102 [] := by kernel_rfl

theorem native.checked102 :
    equal (CleanExpression.polynomial native.placement native.expression102)
        (combination native.relations native.witness102) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression102 native.witness102
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    102 (by decide +kernel) native.idealCodeBinding102 native.idealRelationsBinding native.idealWitnessBinding102
end Airbender.Compiler.CleanArithmeticNative.BigintCached
