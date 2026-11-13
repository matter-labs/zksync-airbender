module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part095
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

local instance generatedBatch96Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch96Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding139 :
    CleanIdealChecks.encode native.placement native.expression139 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 139 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding139 :
    NumericPolynomialChecks.encodeCombination native.witness139 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 139 [] := by kernel_rfl

theorem native.idealInputsBinding139 :
    CleanExpression.inputs native.expression139 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 139 [] := by kernel_rfl

theorem native.checked139 :
    equal (CleanExpression.polynomial native.placement native.expression139)
        (combination native.relations native.witness139) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression139 native.witness139
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 139 (by decide +kernel) native.idealCodeBinding139
    native.idealRelationsBinding native.idealWitnessBinding139

theorem native.preserved139 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression139).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression139 native.placement native.relations native.witness139
    native.checked139 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression140 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨291⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨291⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness140 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨230, by decide⟩)]

theorem native.idealCodeBinding140 :
    CleanIdealChecks.encode native.placement native.expression140 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 140 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding140 :
    NumericPolynomialChecks.encodeCombination native.witness140 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 140 [] := by kernel_rfl

theorem native.idealInputsBinding140 :
    CleanExpression.inputs native.expression140 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 140 [] := by kernel_rfl

theorem native.checked140 :
    equal (CleanExpression.polynomial native.placement native.expression140)
        (combination native.relations native.witness140) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression140 native.witness140
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 140 (by decide +kernel) native.idealCodeBinding140
    native.idealRelationsBinding native.idealWitnessBinding140

theorem native.preserved140 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression140).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression140 native.placement native.relations native.witness140
    native.checked140 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression141 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨308⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨308⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness141 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨231, by decide⟩)]

theorem native.idealCodeBinding141 :
    CleanIdealChecks.encode native.placement native.expression141 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 141 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding141 :
    NumericPolynomialChecks.encodeCombination native.witness141 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 141 [] := by kernel_rfl

theorem native.idealInputsBinding141 :
    CleanExpression.inputs native.expression141 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 141 [] := by kernel_rfl

theorem native.checked141 :
    equal (CleanExpression.polynomial native.placement native.expression141)
        (combination native.relations native.witness141) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression141 native.witness141
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 141 (by decide +kernel) native.idealCodeBinding141
    native.idealRelationsBinding native.idealWitnessBinding141

theorem native.preserved141 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression141).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression141 native.placement native.relations native.witness141
    native.checked141 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression142 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨311⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨311⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness142 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨232, by decide⟩)]

theorem native.idealCodeBinding142 :
    CleanIdealChecks.encode native.placement native.expression142 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 142 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding142 :
    NumericPolynomialChecks.encodeCombination native.witness142 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 142 [] := by kernel_rfl

theorem native.idealInputsBinding142 :
    CleanExpression.inputs native.expression142 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 142 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
