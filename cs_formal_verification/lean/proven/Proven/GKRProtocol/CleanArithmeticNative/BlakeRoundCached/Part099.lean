module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part098
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

local instance generatedBatch99Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch99Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealInputsBinding149 :
    CleanExpression.inputs native.expression149 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 149 [] := by kernel_rfl

theorem native.checked149 :
    equal (CleanExpression.polynomial native.placement native.expression149)
        (combination native.relations native.witness149) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression149 native.witness149
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 149 (by decide +kernel) native.idealCodeBinding149
    native.idealRelationsBinding native.idealWitnessBinding149

theorem native.preserved149 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression149).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression149 native.placement native.relations native.witness149
    native.checked149 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression150 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨391⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨391⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness150 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨240, by decide⟩)]

theorem native.idealCodeBinding150 :
    CleanIdealChecks.encode native.placement native.expression150 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 150 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding150 :
    NumericPolynomialChecks.encodeCombination native.witness150 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 150 [] := by kernel_rfl

theorem native.idealInputsBinding150 :
    CleanExpression.inputs native.expression150 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 150 [] := by kernel_rfl

theorem native.checked150 :
    equal (CleanExpression.polynomial native.placement native.expression150)
        (combination native.relations native.witness150) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression150 native.witness150
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 150 (by decide +kernel) native.idealCodeBinding150
    native.idealRelationsBinding native.idealWitnessBinding150

theorem native.preserved150 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression150).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression150 native.placement native.relations native.witness150
    native.checked150 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression151 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨409⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨409⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness151 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨241, by decide⟩)]

theorem native.idealCodeBinding151 :
    CleanIdealChecks.encode native.placement native.expression151 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 151 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding151 :
    NumericPolynomialChecks.encodeCombination native.witness151 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 151 [] := by kernel_rfl

theorem native.idealInputsBinding151 :
    CleanExpression.inputs native.expression151 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 151 [] := by kernel_rfl

theorem native.checked151 :
    equal (CleanExpression.polynomial native.placement native.expression151)
        (combination native.relations native.witness151) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression151 native.witness151
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 151 (by decide +kernel) native.idealCodeBinding151
    native.idealRelationsBinding native.idealWitnessBinding151

theorem native.preserved151 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression151).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression151 native.placement native.relations native.witness151
    native.checked151 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression152 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨411⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨411⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness152 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨242, by decide⟩)]

theorem native.idealCodeBinding152 :
    CleanIdealChecks.encode native.placement native.expression152 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 152 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding152 :
    NumericPolynomialChecks.encodeCombination native.witness152 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 152 [] := by kernel_rfl

theorem native.idealInputsBinding152 :
    CleanExpression.inputs native.expression152 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 152 [] := by kernel_rfl

theorem native.checked152 :
    equal (CleanExpression.polynomial native.placement native.expression152)
        (combination native.relations native.witness152) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression152 native.witness152
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 152 (by decide +kernel) native.idealCodeBinding152
    native.idealRelationsBinding native.idealWitnessBinding152

theorem native.preserved152 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression152).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression152 native.placement native.relations native.witness152
    native.checked152 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
