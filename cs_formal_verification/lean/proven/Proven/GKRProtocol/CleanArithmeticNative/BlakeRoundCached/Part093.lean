module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
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

local instance generatedBatch93Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch93Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.expression129 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨144⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨144⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness129 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨219, by decide⟩)]

theorem native.idealCodeBinding129 :
    CleanIdealChecks.encode native.placement native.expression129 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 129 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding129 :
    NumericPolynomialChecks.encodeCombination native.witness129 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 129 [] := by kernel_rfl

theorem native.idealInputsBinding129 :
    CleanExpression.inputs native.expression129 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 129 [] := by kernel_rfl

theorem native.checked129 :
    equal (CleanExpression.polynomial native.placement native.expression129)
        (combination native.relations native.witness129) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression129 native.witness129
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 129 (by decide +kernel) native.idealCodeBinding129
    native.idealRelationsBinding native.idealWitnessBinding129

theorem native.preserved129 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression129).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression129 native.placement native.relations native.witness129
    native.checked129 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression130 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨145⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨145⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness130 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨220, by decide⟩)]

theorem native.idealCodeBinding130 :
    CleanIdealChecks.encode native.placement native.expression130 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 130 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding130 :
    NumericPolynomialChecks.encodeCombination native.witness130 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 130 [] := by kernel_rfl

theorem native.idealInputsBinding130 :
    CleanExpression.inputs native.expression130 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 130 [] := by kernel_rfl

theorem native.checked130 :
    equal (CleanExpression.polynomial native.placement native.expression130)
        (combination native.relations native.witness130) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression130 native.witness130
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 130 (by decide +kernel) native.idealCodeBinding130
    native.idealRelationsBinding native.idealWitnessBinding130

theorem native.preserved130 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression130).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression130 native.placement native.relations native.witness130
    native.checked130 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression131 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨146⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨146⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness131 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨221, by decide⟩)]

theorem native.idealCodeBinding131 :
    CleanIdealChecks.encode native.placement native.expression131 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 131 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding131 :
    NumericPolynomialChecks.encodeCombination native.witness131 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 131 [] := by kernel_rfl

theorem native.idealInputsBinding131 :
    CleanExpression.inputs native.expression131 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 131 [] := by kernel_rfl

theorem native.checked131 :
    equal (CleanExpression.polynomial native.placement native.expression131)
        (combination native.relations native.witness131) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression131 native.witness131
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 131 (by decide +kernel) native.idealCodeBinding131
    native.idealRelationsBinding native.idealWitnessBinding131

theorem native.preserved131 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression131).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression131 native.placement native.relations native.witness131
    native.checked131 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression132 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨147⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨147⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness132 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨222, by decide⟩)]

theorem native.idealCodeBinding132 :
    CleanIdealChecks.encode native.placement native.expression132 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 132 (.constant 0) := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
