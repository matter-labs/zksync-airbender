module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part111
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

local instance generatedBatch112Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch112Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness194 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨284, by decide⟩)]

theorem native.idealCodeBinding194 :
    CleanIdealChecks.encode native.placement native.expression194 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 194 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding194 :
    NumericPolynomialChecks.encodeCombination native.witness194 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 194 [] := by kernel_rfl

theorem native.idealInputsBinding194 :
    CleanExpression.inputs native.expression194 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 194 [] := by kernel_rfl

theorem native.checked194 :
    equal (CleanExpression.polynomial native.placement native.expression194)
        (combination native.relations native.witness194) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression194 native.witness194
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 194 (by decide +kernel) native.idealCodeBinding194
    native.idealRelationsBinding native.idealWitnessBinding194

theorem native.preserved194 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression194).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression194 native.placement native.relations native.witness194
    native.checked194 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression195 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨688⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨688⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness195 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨285, by decide⟩)]

theorem native.idealCodeBinding195 :
    CleanIdealChecks.encode native.placement native.expression195 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 195 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding195 :
    NumericPolynomialChecks.encodeCombination native.witness195 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 195 [] := by kernel_rfl

theorem native.idealInputsBinding195 :
    CleanExpression.inputs native.expression195 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 195 [] := by kernel_rfl

theorem native.checked195 :
    equal (CleanExpression.polynomial native.placement native.expression195)
        (combination native.relations native.witness195) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression195 native.witness195
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 195 (by decide +kernel) native.idealCodeBinding195
    native.idealRelationsBinding native.idealWitnessBinding195

theorem native.preserved195 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression195).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression195 native.placement native.relations native.witness195
    native.checked195 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression196 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨691⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨691⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness196 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨286, by decide⟩)]

theorem native.idealCodeBinding196 :
    CleanIdealChecks.encode native.placement native.expression196 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 196 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding196 :
    NumericPolynomialChecks.encodeCombination native.witness196 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 196 [] := by kernel_rfl

theorem native.idealInputsBinding196 :
    CleanExpression.inputs native.expression196 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 196 [] := by kernel_rfl

theorem native.checked196 :
    equal (CleanExpression.polynomial native.placement native.expression196)
        (combination native.relations native.witness196) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression196 native.witness196
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 196 (by decide +kernel) native.idealCodeBinding196
    native.idealRelationsBinding native.idealWitnessBinding196

theorem native.preserved196 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression196).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression196 native.placement native.relations native.witness196
    native.checked196 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression197 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨694⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨694⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness197 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨287, by decide⟩)]

theorem native.idealCodeBinding197 :
    CleanIdealChecks.encode native.placement native.expression197 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 197 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding197 :
    NumericPolynomialChecks.encodeCombination native.witness197 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 197 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
