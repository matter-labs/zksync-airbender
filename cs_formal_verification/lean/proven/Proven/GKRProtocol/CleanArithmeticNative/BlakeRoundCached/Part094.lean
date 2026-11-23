module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part093
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

local instance generatedBatch94Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch94Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealWitnessBinding132 :
    NumericPolynomialChecks.encodeCombination native.witness132 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 132 [] := by kernel_rfl

theorem native.idealInputsBinding132 :
    CleanExpression.inputs native.expression132 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 132 [] := by kernel_rfl

theorem native.checked132 :
    equal (CleanExpression.polynomial native.placement native.expression132)
        (combination native.relations native.witness132) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression132 native.witness132
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 132 (by decide +kernel) native.idealCodeBinding132
    native.idealRelationsBinding native.idealWitnessBinding132

theorem native.preserved132 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression132).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression132 native.placement native.relations native.witness132
    native.checked132 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression133 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨148⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨148⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness133 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨223, by decide⟩)]

theorem native.idealCodeBinding133 :
    CleanIdealChecks.encode native.placement native.expression133 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 133 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding133 :
    NumericPolynomialChecks.encodeCombination native.witness133 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 133 [] := by kernel_rfl

theorem native.idealInputsBinding133 :
    CleanExpression.inputs native.expression133 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 133 [] := by kernel_rfl

theorem native.checked133 :
    equal (CleanExpression.polynomial native.placement native.expression133)
        (combination native.relations native.witness133) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression133 native.witness133
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 133 (by decide +kernel) native.idealCodeBinding133
    native.idealRelationsBinding native.idealWitnessBinding133

theorem native.preserved133 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression133).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression133 native.placement native.relations native.witness133
    native.checked133 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression134 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨149⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨149⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness134 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨224, by decide⟩)]

theorem native.idealCodeBinding134 :
    CleanIdealChecks.encode native.placement native.expression134 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 134 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding134 :
    NumericPolynomialChecks.encodeCombination native.witness134 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 134 [] := by kernel_rfl

theorem native.idealInputsBinding134 :
    CleanExpression.inputs native.expression134 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 134 [] := by kernel_rfl

theorem native.checked134 :
    equal (CleanExpression.polynomial native.placement native.expression134)
        (combination native.relations native.witness134) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression134 native.witness134
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 134 (by decide +kernel) native.idealCodeBinding134
    native.idealRelationsBinding native.idealWitnessBinding134

theorem native.preserved134 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression134).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression134 native.placement native.relations native.witness134
    native.checked134 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression135 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨150⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨150⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness135 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨225, by decide⟩)]

theorem native.idealCodeBinding135 :
    CleanIdealChecks.encode native.placement native.expression135 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 135 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding135 :
    NumericPolynomialChecks.encodeCombination native.witness135 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 135 [] := by kernel_rfl

theorem native.idealInputsBinding135 :
    CleanExpression.inputs native.expression135 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 135 [] := by kernel_rfl

theorem native.checked135 :
    equal (CleanExpression.polynomial native.placement native.expression135)
        (combination native.relations native.witness135) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression135 native.witness135
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 135 (by decide +kernel) native.idealCodeBinding135
    native.idealRelationsBinding native.idealWitnessBinding135
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
