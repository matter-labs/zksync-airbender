module
public import Proven.KernelRfl
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part033
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part034
public import Proven.GKRProtocol.CleanArithmeticNative.BlakeRoundCached.Part097
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

local instance generatedBatch98Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch98Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.witness146 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨236, by decide⟩)]

theorem native.idealCodeBinding146 :
    CleanIdealChecks.encode native.placement native.expression146 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 146 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding146 :
    NumericPolynomialChecks.encodeCombination native.witness146 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 146 [] := by kernel_rfl

theorem native.idealInputsBinding146 :
    CleanExpression.inputs native.expression146 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 146 [] := by kernel_rfl

theorem native.checked146 :
    equal (CleanExpression.polynomial native.placement native.expression146)
        (combination native.relations native.witness146) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression146 native.witness146
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 146 (by decide +kernel) native.idealCodeBinding146
    native.idealRelationsBinding native.idealWitnessBinding146

theorem native.preserved146 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression146).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression146 native.placement native.relations native.witness146
    native.checked146 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression147 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨369⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨369⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness147 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨237, by decide⟩)]

theorem native.idealCodeBinding147 :
    CleanIdealChecks.encode native.placement native.expression147 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 147 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding147 :
    NumericPolynomialChecks.encodeCombination native.witness147 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 147 [] := by kernel_rfl

theorem native.idealInputsBinding147 :
    CleanExpression.inputs native.expression147 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 147 [] := by kernel_rfl

theorem native.checked147 :
    equal (CleanExpression.polynomial native.placement native.expression147)
        (combination native.relations native.witness147) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression147 native.witness147
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 147 (by decide +kernel) native.idealCodeBinding147
    native.idealRelationsBinding native.idealWitnessBinding147

theorem native.preserved147 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression147).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression147 native.placement native.relations native.witness147
    native.checked147 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression148 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨371⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨371⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness148 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨238, by decide⟩)]

theorem native.idealCodeBinding148 :
    CleanIdealChecks.encode native.placement native.expression148 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 148 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding148 :
    NumericPolynomialChecks.encodeCombination native.witness148 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 148 [] := by kernel_rfl

theorem native.idealInputsBinding148 :
    CleanExpression.inputs native.expression148 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 148 [] := by kernel_rfl

theorem native.checked148 :
    equal (CleanExpression.polynomial native.placement native.expression148)
        (combination native.relations native.witness148) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression148 native.witness148
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 148 (by decide +kernel) native.idealCodeBinding148
    native.idealRelationsBinding native.idealWitnessBinding148

theorem native.preserved148 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression148).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression148 native.placement native.relations native.witness148
    native.checked148 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression149 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨388⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨388⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness149 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨239, by decide⟩)]

theorem native.idealCodeBinding149 :
    CleanIdealChecks.encode native.placement native.expression149 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 149 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding149 :
    NumericPolynomialChecks.encodeCombination native.witness149 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 149 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
