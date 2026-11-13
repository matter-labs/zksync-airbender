module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part116
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

local instance generatedBatch117Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch117Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding211 :
    CleanIdealChecks.encode native.placement native.expression211 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 211 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding211 :
    NumericPolynomialChecks.encodeCombination native.witness211 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 211 [] := by kernel_rfl

theorem native.idealInputsBinding211 :
    CleanExpression.inputs native.expression211 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 211 [] := by kernel_rfl

theorem native.checked211 :
    equal (CleanExpression.polynomial native.placement native.expression211)
        (combination native.relations native.witness211) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression211 native.witness211
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 211 (by decide +kernel) native.idealCodeBinding211
    native.idealRelationsBinding native.idealWitnessBinding211

theorem native.preserved211 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression211).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression211 native.placement native.relations native.witness211
    native.checked211 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression212 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨739⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨739⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness212 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨302, by decide⟩)]

theorem native.idealCodeBinding212 :
    CleanIdealChecks.encode native.placement native.expression212 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 212 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding212 :
    NumericPolynomialChecks.encodeCombination native.witness212 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 212 [] := by kernel_rfl

theorem native.idealInputsBinding212 :
    CleanExpression.inputs native.expression212 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 212 [] := by kernel_rfl

theorem native.checked212 :
    equal (CleanExpression.polynomial native.placement native.expression212)
        (combination native.relations native.witness212) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression212 native.witness212
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 212 (by decide +kernel) native.idealCodeBinding212
    native.idealRelationsBinding native.idealWitnessBinding212

theorem native.preserved212 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression212).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression212 native.placement native.relations native.witness212
    native.checked212 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression213 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨742⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨742⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness213 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨303, by decide⟩)]

theorem native.idealCodeBinding213 :
    CleanIdealChecks.encode native.placement native.expression213 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 213 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding213 :
    NumericPolynomialChecks.encodeCombination native.witness213 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 213 [] := by kernel_rfl

theorem native.idealInputsBinding213 :
    CleanExpression.inputs native.expression213 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 213 [] := by kernel_rfl

theorem native.checked213 :
    equal (CleanExpression.polynomial native.placement native.expression213)
        (combination native.relations native.witness213) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression213 native.witness213
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 213 (by decide +kernel) native.idealCodeBinding213
    native.idealRelationsBinding native.idealWitnessBinding213

theorem native.preserved213 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression213).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression213 native.placement native.relations native.witness213
    native.checked213 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression214 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨745⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨745⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness214 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨304, by decide⟩)]

theorem native.idealCodeBinding214 :
    CleanIdealChecks.encode native.placement native.expression214 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 214 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding214 :
    NumericPolynomialChecks.encodeCombination native.witness214 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 214 [] := by kernel_rfl

theorem native.idealInputsBinding214 :
    CleanExpression.inputs native.expression214 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 214 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
