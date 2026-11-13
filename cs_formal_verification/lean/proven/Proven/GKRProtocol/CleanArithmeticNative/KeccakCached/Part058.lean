module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part057
public import Proven.KernelRfl
import all Mathlib.Data.List.Sort
public import Proven.Import.GKRProtocol.CleanArithmeticImport
public import Proven.GKRProtocol.CleanIdealNative.KeccakCached
public import Proven.GKRProtocol.FullArithmeticNative.KeccakCached
public import Proven.GKRProtocol.CleanPlacementNative.KeccakCached

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArithmeticNative.KeccakCached
open Airbender Airbender.Compiler
set_option maxRecDepth 32768

local instance generatedBatch58Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch58Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealInputsBinding153 :
    CleanExpression.inputs native.expression153 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 153 [] := by kernel_rfl

theorem native.checked153 :
    equal (CleanExpression.polynomial native.placement native.expression153)
        (combination native.relations native.witness153) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression153 native.witness153
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    153 (by decide +kernel) native.idealCodeBinding153 native.idealRelationsBinding native.idealWitnessBinding153

theorem native.preserved153 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression153).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression153 native.placement native.relations native.witness153
    native.checked153 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression154 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨59⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨61⟩))))
    (Airbender.Expression.var ⟨69⟩)

noncomputable def native.witness154 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨186, by decide⟩)]

theorem native.idealCodeBinding154 :
    CleanIdealChecks.encode native.placement native.expression154 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 154 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding154 :
    NumericPolynomialChecks.encodeCombination native.witness154 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 154 [] := by kernel_rfl

theorem native.idealInputsBinding154 :
    CleanExpression.inputs native.expression154 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 154 [] := by kernel_rfl

theorem native.checked154 :
    equal (CleanExpression.polynomial native.placement native.expression154)
        (combination native.relations native.witness154) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression154 native.witness154
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    154 (by decide +kernel) native.idealCodeBinding154 native.idealRelationsBinding native.idealWitnessBinding154

theorem native.preserved154 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression154).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression154 native.placement native.relations native.witness154
    native.checked154 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression155 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨60⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨62⟩))))
    (Airbender.Expression.var ⟨69⟩)

noncomputable def native.witness155 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨187, by decide⟩)]

theorem native.idealCodeBinding155 :
    CleanIdealChecks.encode native.placement native.expression155 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 155 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding155 :
    NumericPolynomialChecks.encodeCombination native.witness155 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 155 [] := by kernel_rfl

theorem native.idealInputsBinding155 :
    CleanExpression.inputs native.expression155 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 155 [] := by kernel_rfl

theorem native.checked155 :
    equal (CleanExpression.polynomial native.placement native.expression155)
        (combination native.relations native.witness155) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression155 native.witness155
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    155 (by decide +kernel) native.idealCodeBinding155 native.idealRelationsBinding native.idealWitnessBinding155

theorem native.preserved155 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression155).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression155 native.placement native.relations native.witness155
    native.checked155 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression156 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.var ⟨63⟩))
    (Airbender.Expression.add
      (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
        (Airbender.Expression.var ⟨63⟩))
      (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))

noncomputable def native.witness156 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨188, by decide⟩)]

theorem native.idealCodeBinding156 :
    CleanIdealChecks.encode native.placement native.expression156 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 156 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding156 :
    NumericPolynomialChecks.encodeCombination native.witness156 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 156 [] := by kernel_rfl

theorem native.idealInputsBinding156 :
    CleanExpression.inputs native.expression156 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 156 [] := by kernel_rfl

theorem native.checked156 :
    equal (CleanExpression.polynomial native.placement native.expression156)
        (combination native.relations native.witness156) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression156 native.witness156
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    156 (by decide +kernel) native.idealCodeBinding156 native.idealRelationsBinding native.idealWitnessBinding156

theorem native.preserved156 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression156).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression156 native.placement native.relations native.witness156
    native.checked156 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
