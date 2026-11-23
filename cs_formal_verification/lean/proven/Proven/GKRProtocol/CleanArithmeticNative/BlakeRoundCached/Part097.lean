module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part096
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

local instance generatedBatch97Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch97Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.checked142 :
    equal (CleanExpression.polynomial native.placement native.expression142)
        (combination native.relations native.witness142) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression142 native.witness142
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 142 (by decide +kernel) native.idealCodeBinding142
    native.idealRelationsBinding native.idealWitnessBinding142

theorem native.preserved142 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression142).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression142 native.placement native.relations native.witness142
    native.checked142 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression143 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨329⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨329⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness143 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨233, by decide⟩)]

theorem native.idealCodeBinding143 :
    CleanIdealChecks.encode native.placement native.expression143 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 143 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding143 :
    NumericPolynomialChecks.encodeCombination native.witness143 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 143 [] := by kernel_rfl

theorem native.idealInputsBinding143 :
    CleanExpression.inputs native.expression143 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 143 [] := by kernel_rfl

theorem native.checked143 :
    equal (CleanExpression.polynomial native.placement native.expression143)
        (combination native.relations native.witness143) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression143 native.witness143
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 143 (by decide +kernel) native.idealCodeBinding143
    native.idealRelationsBinding native.idealWitnessBinding143

theorem native.preserved143 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression143).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression143 native.placement native.relations native.witness143
    native.checked143 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression144 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨331⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨331⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness144 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨234, by decide⟩)]

theorem native.idealCodeBinding144 :
    CleanIdealChecks.encode native.placement native.expression144 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 144 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding144 :
    NumericPolynomialChecks.encodeCombination native.witness144 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 144 [] := by kernel_rfl

theorem native.idealInputsBinding144 :
    CleanExpression.inputs native.expression144 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 144 [] := by kernel_rfl

theorem native.checked144 :
    equal (CleanExpression.polynomial native.placement native.expression144)
        (combination native.relations native.witness144) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression144 native.witness144
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 144 (by decide +kernel) native.idealCodeBinding144
    native.idealRelationsBinding native.idealWitnessBinding144

theorem native.preserved144 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression144).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression144 native.placement native.relations native.witness144
    native.checked144 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression145 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨348⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨348⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness145 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨235, by decide⟩)]

theorem native.idealCodeBinding145 :
    CleanIdealChecks.encode native.placement native.expression145 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 145 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding145 :
    NumericPolynomialChecks.encodeCombination native.witness145 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 145 [] := by kernel_rfl

theorem native.idealInputsBinding145 :
    CleanExpression.inputs native.expression145 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 145 [] := by kernel_rfl

theorem native.checked145 :
    equal (CleanExpression.polynomial native.placement native.expression145)
        (combination native.relations native.witness145) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression145 native.witness145
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 145 (by decide +kernel) native.idealCodeBinding145
    native.idealRelationsBinding native.idealWitnessBinding145

theorem native.preserved145 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression145).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression145 native.placement native.relations native.witness145
    native.checked145 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression146 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨351⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨351⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
