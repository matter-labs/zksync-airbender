module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part053
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

local instance generatedBatch54Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch54Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.preserved67 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression67).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression67 native.placement native.relations native.witness67
    native.checked67 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression68 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨146⟩))
        (Airbender.Expression.var ⟨202⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨218⟩))

noncomputable def native.witness68 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨158, by decide⟩)]

theorem native.idealCodeBinding68 :
    CleanIdealChecks.encode native.placement native.expression68 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 68 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding68 :
    NumericPolynomialChecks.encodeCombination native.witness68 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 68 [] := by kernel_rfl

theorem native.idealInputsBinding68 :
    CleanExpression.inputs native.expression68 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 68 [] := by kernel_rfl

theorem native.checked68 :
    equal (CleanExpression.polynomial native.placement native.expression68)
        (combination native.relations native.witness68) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression68 native.witness68
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 68 (by decide +kernel) native.idealCodeBinding68
    native.idealRelationsBinding native.idealWitnessBinding68

theorem native.preserved68 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression68).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression68 native.placement native.relations native.witness68
    native.checked68 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression69 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨147⟩))
        (Airbender.Expression.var ⟨202⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨219⟩))

noncomputable def native.witness69 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨159, by decide⟩)]

theorem native.idealCodeBinding69 :
    CleanIdealChecks.encode native.placement native.expression69 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 69 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding69 :
    NumericPolynomialChecks.encodeCombination native.witness69 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 69 [] := by kernel_rfl

theorem native.idealInputsBinding69 :
    CleanExpression.inputs native.expression69 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 69 [] := by kernel_rfl

theorem native.checked69 :
    equal (CleanExpression.polynomial native.placement native.expression69)
        (combination native.relations native.witness69) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression69 native.witness69
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 69 (by decide +kernel) native.idealCodeBinding69
    native.idealRelationsBinding native.idealWitnessBinding69

theorem native.preserved69 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression69).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression69 native.placement native.relations native.witness69
    native.checked69 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression70 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨148⟩))
        (Airbender.Expression.var ⟨202⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨220⟩))

noncomputable def native.witness70 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨160, by decide⟩)]

theorem native.idealCodeBinding70 :
    CleanIdealChecks.encode native.placement native.expression70 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 70 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding70 :
    NumericPolynomialChecks.encodeCombination native.witness70 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 70 [] := by kernel_rfl

theorem native.idealInputsBinding70 :
    CleanExpression.inputs native.expression70 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 70 [] := by kernel_rfl

theorem native.checked70 :
    equal (CleanExpression.polynomial native.placement native.expression70)
        (combination native.relations native.witness70) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression70 native.witness70
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 70 (by decide +kernel) native.idealCodeBinding70
    native.idealRelationsBinding native.idealWitnessBinding70

theorem native.preserved70 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression70).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression70 native.placement native.relations native.witness70
    native.checked70 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression71 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.add
    (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
      (Airbender.Expression.mul
        (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
          (Airbender.Expression.var ⟨149⟩))
        (Airbender.Expression.var ⟨202⟩)))
    (Airbender.Expression.mul
      (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
        (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
      (Airbender.Expression.var ⟨221⟩))

noncomputable def native.witness71 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨161, by decide⟩)]
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
