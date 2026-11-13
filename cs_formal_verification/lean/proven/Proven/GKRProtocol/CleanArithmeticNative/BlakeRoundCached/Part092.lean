module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part091
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

local instance generatedBatch92Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch92Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealInputsBinding125 :
    CleanExpression.inputs native.expression125 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 125 [] := by kernel_rfl

theorem native.checked125 :
    equal (CleanExpression.polynomial native.placement native.expression125)
        (combination native.relations native.witness125) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression125 native.witness125
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 125 (by decide +kernel) native.idealCodeBinding125
    native.idealRelationsBinding native.idealWitnessBinding125

theorem native.preserved125 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression125).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression125 native.placement native.relations native.witness125
    native.checked125 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression126 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨141⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨141⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness126 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨216, by decide⟩)]

theorem native.idealCodeBinding126 :
    CleanIdealChecks.encode native.placement native.expression126 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 126 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding126 :
    NumericPolynomialChecks.encodeCombination native.witness126 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 126 [] := by kernel_rfl

theorem native.idealInputsBinding126 :
    CleanExpression.inputs native.expression126 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 126 [] := by kernel_rfl

theorem native.checked126 :
    equal (CleanExpression.polynomial native.placement native.expression126)
        (combination native.relations native.witness126) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression126 native.witness126
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 126 (by decide +kernel) native.idealCodeBinding126
    native.idealRelationsBinding native.idealWitnessBinding126

theorem native.preserved126 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression126).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression126 native.placement native.relations native.witness126
    native.checked126 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression127 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨142⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨142⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness127 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨217, by decide⟩)]

theorem native.idealCodeBinding127 :
    CleanIdealChecks.encode native.placement native.expression127 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 127 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding127 :
    NumericPolynomialChecks.encodeCombination native.witness127 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 127 [] := by kernel_rfl

theorem native.idealInputsBinding127 :
    CleanExpression.inputs native.expression127 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 127 [] := by kernel_rfl

theorem native.checked127 :
    equal (CleanExpression.polynomial native.placement native.expression127)
        (combination native.relations native.witness127) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression127 native.witness127
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 127 (by decide +kernel) native.idealCodeBinding127
    native.idealRelationsBinding native.idealWitnessBinding127

theorem native.preserved127 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression127).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression127 native.placement native.relations native.witness127
    native.checked127 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression128 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨143⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨143⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness128 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨218, by decide⟩)]

theorem native.idealCodeBinding128 :
    CleanIdealChecks.encode native.placement native.expression128 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 128 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding128 :
    NumericPolynomialChecks.encodeCombination native.witness128 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 128 [] := by kernel_rfl

theorem native.idealInputsBinding128 :
    CleanExpression.inputs native.expression128 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 128 [] := by kernel_rfl

theorem native.checked128 :
    equal (CleanExpression.polynomial native.placement native.expression128)
        (combination native.relations native.witness128) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression128 native.witness128
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 128 (by decide +kernel) native.idealCodeBinding128
    native.idealRelationsBinding native.idealWitnessBinding128

theorem native.preserved128 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression128).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression128 native.placement native.relations native.witness128
    native.checked128 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
