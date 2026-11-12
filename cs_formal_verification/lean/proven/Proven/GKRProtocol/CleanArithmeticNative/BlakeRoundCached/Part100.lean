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

local instance generatedBatch100Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch100Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.expression153 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨426⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨426⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness153 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨243, by decide⟩)]

theorem native.idealCodeBinding153 :
    CleanIdealChecks.encode native.placement native.expression153 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 153 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding153 :
    NumericPolynomialChecks.encodeCombination native.witness153 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 153 [] := by kernel_rfl

theorem native.idealInputsBinding153 :
    CleanExpression.inputs native.expression153 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 153 [] := by kernel_rfl

theorem native.checked153 :
    equal (CleanExpression.polynomial native.placement native.expression153)
        (combination native.relations native.witness153) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression153 native.witness153
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 153 (by decide +kernel) native.idealCodeBinding153
    native.idealRelationsBinding native.idealWitnessBinding153

theorem native.preserved153 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression153).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression153 native.placement native.relations native.witness153
    native.checked153 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression154 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨429⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨429⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness154 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨244, by decide⟩)]

theorem native.idealCodeBinding154 :
    CleanIdealChecks.encode native.placement native.expression154 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 154 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding154 :
    NumericPolynomialChecks.encodeCombination native.witness154 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 154 [] := by kernel_rfl

theorem native.idealInputsBinding154 :
    CleanExpression.inputs native.expression154 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 154 [] := by kernel_rfl

theorem native.checked154 :
    equal (CleanExpression.polynomial native.placement native.expression154)
        (combination native.relations native.witness154) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression154 native.witness154
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 154 (by decide +kernel) native.idealCodeBinding154
    native.idealRelationsBinding native.idealWitnessBinding154

theorem native.preserved154 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression154).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression154 native.placement native.relations native.witness154
    native.checked154 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression155 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨456⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨456⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness155 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨245, by decide⟩)]

theorem native.idealCodeBinding155 :
    CleanIdealChecks.encode native.placement native.expression155 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 155 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding155 :
    NumericPolynomialChecks.encodeCombination native.witness155 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).witnesses.getD 155 [] := by kernel_rfl

theorem native.idealInputsBinding155 :
    CleanExpression.inputs native.expression155 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).inputs.getD 155 [] := by kernel_rfl

theorem native.checked155 :
    equal (CleanExpression.polynomial native.placement native.expression155)
        (combination native.relations native.witness155) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression155 native.witness155
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture
    Airbender.Compiler.CleanIdealNative.BlakeRoundCached.checked 155 (by decide +kernel) native.idealCodeBinding155
    native.idealRelationsBinding native.idealWitnessBinding155

theorem native.preserved155 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address)) :
    (native.expression155).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression155 native.placement native.relations native.witness155
    native.checked155 (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank).address base data holds

noncomputable def native.expression156 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨459⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨459⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness156 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨246, by decide⟩)]

theorem native.idealCodeBinding156 :
    CleanIdealChecks.encode native.placement native.expression156 =
      (Airbender.Compiler.CleanIdealNative.BlakeRoundCached.capture).codes.getD 156 (.constant 0) := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached
