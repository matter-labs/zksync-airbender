module
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.BigintCached.Part080
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.BigintCached
public import Proven.GKRProtocol.FullArithmeticNative.BigintCached
public import Proven.GKRProtocol.CleanPlacementNative.BigintCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.BigintCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch81Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch81Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealInputsBinding116 :
    CleanExpression.inputs native.expression116 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 116 [] := by kernel_rfl

theorem native.checked116 :
    equal (CleanExpression.polynomial native.placement native.expression116)
        (combination native.relations native.witness116) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression116 native.witness116
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    116 (by decide +kernel) native.idealCodeBinding116 native.idealRelationsBinding native.idealWitnessBinding116

theorem native.preserved116 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression116).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression116 native.placement native.relations native.witness116
    native.checked116 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression117 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨221⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨221⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness117 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨158, by decide⟩)]

theorem native.idealCodeBinding117 :
    CleanIdealChecks.encode native.placement native.expression117 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 117 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding117 :
    NumericPolynomialChecks.encodeCombination native.witness117 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 117 [] := by kernel_rfl

theorem native.idealInputsBinding117 :
    CleanExpression.inputs native.expression117 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 117 [] := by kernel_rfl

theorem native.checked117 :
    equal (CleanExpression.polynomial native.placement native.expression117)
        (combination native.relations native.witness117) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression117 native.witness117
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    117 (by decide +kernel) native.idealCodeBinding117 native.idealRelationsBinding native.idealWitnessBinding117

theorem native.preserved117 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression117).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression117 native.placement native.relations native.witness117
    native.checked117 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression118 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨224⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨224⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness118 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨159, by decide⟩)]

theorem native.idealCodeBinding118 :
    CleanIdealChecks.encode native.placement native.expression118 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 118 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding118 :
    NumericPolynomialChecks.encodeCombination native.witness118 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 118 [] := by kernel_rfl

theorem native.idealInputsBinding118 :
    CleanExpression.inputs native.expression118 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 118 [] := by kernel_rfl

theorem native.checked118 :
    equal (CleanExpression.polynomial native.placement native.expression118)
        (combination native.relations native.witness118) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression118 native.witness118
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    118 (by decide +kernel) native.idealCodeBinding118 native.idealRelationsBinding native.idealWitnessBinding118

theorem native.preserved118 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression118).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression118 native.placement native.relations native.witness118
    native.checked118 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds

noncomputable def native.expression119 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨227⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨227⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness119 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨160, by decide⟩)]

theorem native.idealCodeBinding119 :
    CleanIdealChecks.encode native.placement native.expression119 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).codes.getD 119 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding119 :
    NumericPolynomialChecks.encodeCombination native.witness119 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).witnesses.getD 119 [] := by kernel_rfl

theorem native.idealInputsBinding119 :
    CleanExpression.inputs native.expression119 =
      (Airbender.Compiler.CleanIdealNative.BigintCached.capture).inputs.getD 119 [] := by kernel_rfl

theorem native.checked119 :
    equal (CleanExpression.polynomial native.placement native.expression119)
        (combination native.relations native.witness119) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression119 native.witness119
    Airbender.Compiler.CleanIdealNative.BigintCached.capture Airbender.Compiler.CleanIdealNative.BigintCached.checked
    119 (by decide +kernel) native.idealCodeBinding119 native.idealRelationsBinding native.idealWitnessBinding119

theorem native.preserved119 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address)) :
    (native.expression119).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression119 native.placement native.relations native.witness119
    native.checked119 (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.BigintCached
