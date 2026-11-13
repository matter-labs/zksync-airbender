module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part094
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

local instance generatedBatch95Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch95Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.preserved135 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression135).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression135 native.placement native.relations native.witness135
    native.checked135 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression136 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨151⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨151⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness136 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨226, by decide⟩)]

theorem native.idealCodeBinding136 :
    CleanIdealChecks.encode native.placement native.expression136 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 136 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding136 :
    NumericPolynomialChecks.encodeCombination native.witness136 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 136 [] := by kernel_rfl

theorem native.idealInputsBinding136 :
    CleanExpression.inputs native.expression136 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 136 [] := by kernel_rfl

theorem native.checked136 :
    equal (CleanExpression.polynomial native.placement native.expression136)
        (combination native.relations native.witness136) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression136 native.witness136
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 136 (by decide +kernel) native.idealCodeBinding136
    native.idealRelationsBinding native.idealWitnessBinding136

theorem native.preserved136 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression136).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression136 native.placement native.relations native.witness136
    native.checked136 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression137 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨268⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨268⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness137 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨227, by decide⟩)]

theorem native.idealCodeBinding137 :
    CleanIdealChecks.encode native.placement native.expression137 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 137 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding137 :
    NumericPolynomialChecks.encodeCombination native.witness137 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 137 [] := by kernel_rfl

theorem native.idealInputsBinding137 :
    CleanExpression.inputs native.expression137 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 137 [] := by kernel_rfl

theorem native.checked137 :
    equal (CleanExpression.polynomial native.placement native.expression137)
        (combination native.relations native.witness137) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression137 native.witness137
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 137 (by decide +kernel) native.idealCodeBinding137
    native.idealRelationsBinding native.idealWitnessBinding137

theorem native.preserved137 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression137).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression137 native.placement native.relations native.witness137
    native.checked137 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression138 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨271⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨271⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness138 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨228, by decide⟩)]

theorem native.idealCodeBinding138 :
    CleanIdealChecks.encode native.placement native.expression138 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 138 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding138 :
    NumericPolynomialChecks.encodeCombination native.witness138 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 138 [] := by kernel_rfl

theorem native.idealInputsBinding138 :
    CleanExpression.inputs native.expression138 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 138 [] := by kernel_rfl

theorem native.checked138 :
    equal (CleanExpression.polynomial native.placement native.expression138)
        (combination native.relations native.witness138) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression138 native.witness138
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 138 (by decide +kernel) native.idealCodeBinding138
    native.idealRelationsBinding native.idealWitnessBinding138

theorem native.preserved138 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression138).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression138 native.placement native.relations native.witness138
    native.checked138 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression139 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨289⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨289⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness139 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨229, by decide⟩)]
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
