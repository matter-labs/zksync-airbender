module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part049
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

local instance generatedBatch50Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch50Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness54 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨144, by decide⟩)]

theorem native.idealCodeBinding54 :
    CleanIdealChecks.encode native.placement native.expression54 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 54 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding54 :
    NumericPolynomialChecks.encodeCombination native.witness54 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 54 [] := by kernel_rfl

theorem native.idealInputsBinding54 :
    CleanExpression.inputs native.expression54 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 54 [] := by kernel_rfl

theorem native.checked54 :
    equal (CleanExpression.polynomial native.placement native.expression54)
        (combination native.relations native.witness54) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression54 native.witness54
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 54 (by decide +kernel) native.idealCodeBinding54
    native.idealRelationsBinding native.idealWitnessBinding54

theorem native.preserved54 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression54).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression54 native.placement native.relations native.witness54
    native.checked54 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression55 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨143⟩))
        (Airbender.Expression.var ⟨203⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨205⟩))

noncomputable def native.witness55 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨145, by decide⟩)]

theorem native.idealCodeBinding55 :
    CleanIdealChecks.encode native.placement native.expression55 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 55 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding55 :
    NumericPolynomialChecks.encodeCombination native.witness55 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 55 [] := by kernel_rfl

theorem native.idealInputsBinding55 :
    CleanExpression.inputs native.expression55 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 55 [] := by kernel_rfl

theorem native.checked55 :
    equal (CleanExpression.polynomial native.placement native.expression55)
        (combination native.relations native.witness55) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression55 native.witness55
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 55 (by decide +kernel) native.idealCodeBinding55
    native.idealRelationsBinding native.idealWitnessBinding55

theorem native.preserved55 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression55).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression55 native.placement native.relations native.witness55
    native.checked55 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression56 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨144⟩))
        (Airbender.Expression.var ⟨203⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨206⟩))

noncomputable def native.witness56 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨146, by decide⟩)]

theorem native.idealCodeBinding56 :
    CleanIdealChecks.encode native.placement native.expression56 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 56 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding56 :
    NumericPolynomialChecks.encodeCombination native.witness56 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 56 [] := by kernel_rfl

theorem native.idealInputsBinding56 :
    CleanExpression.inputs native.expression56 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 56 [] := by kernel_rfl

theorem native.checked56 :
    equal (CleanExpression.polynomial native.placement native.expression56)
        (combination native.relations native.witness56) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression56 native.witness56
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 56 (by decide +kernel) native.idealCodeBinding56
    native.idealRelationsBinding native.idealWitnessBinding56

theorem native.preserved56 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression56).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression56 native.placement native.relations native.witness56
    native.checked56 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression57 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨145⟩))
        (Airbender.Expression.var ⟨203⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨207⟩))

noncomputable def native.witness57 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨147, by decide⟩)]

theorem native.idealCodeBinding57 :
    CleanIdealChecks.encode native.placement native.expression57 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 57 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding57 :
    NumericPolynomialChecks.encodeCombination native.witness57 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 57 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
