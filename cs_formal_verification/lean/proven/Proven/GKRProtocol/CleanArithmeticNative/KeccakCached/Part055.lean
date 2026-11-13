module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part054
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

local instance generatedBatch55Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch55Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.idealCodeBinding143 :
    CleanIdealChecks.encode native.placement native.expression143 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 143 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding143 :
    NumericPolynomialChecks.encodeCombination native.witness143 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 143 [] := by kernel_rfl

theorem native.idealInputsBinding143 :
    CleanExpression.inputs native.expression143 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 143 [] := by kernel_rfl

theorem native.checked143 :
    equal (CleanExpression.polynomial native.placement native.expression143)
        (combination native.relations native.witness143) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression143 native.witness143
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    143 (by decide +kernel) native.idealCodeBinding143 native.idealRelationsBinding native.idealWitnessBinding143

theorem native.preserved143 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression143).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression143 native.placement native.relations native.witness143
    native.checked143 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression144 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨39⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨41⟩))))
    (Airbender.Expression.var ⟨69⟩)

noncomputable def native.witness144 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨176, by decide⟩)]

theorem native.idealCodeBinding144 :
    CleanIdealChecks.encode native.placement native.expression144 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 144 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding144 :
    NumericPolynomialChecks.encodeCombination native.witness144 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 144 [] := by kernel_rfl

theorem native.idealInputsBinding144 :
    CleanExpression.inputs native.expression144 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 144 [] := by kernel_rfl

theorem native.checked144 :
    equal (CleanExpression.polynomial native.placement native.expression144)
        (combination native.relations native.witness144) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression144 native.witness144
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    144 (by decide +kernel) native.idealCodeBinding144 native.idealRelationsBinding native.idealWitnessBinding144

theorem native.preserved144 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression144).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression144 native.placement native.relations native.witness144
    native.checked144 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression145 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨40⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨42⟩))))
    (Airbender.Expression.var ⟨69⟩)

noncomputable def native.witness145 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨177, by decide⟩)]

theorem native.idealCodeBinding145 :
    CleanIdealChecks.encode native.placement native.expression145 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 145 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding145 :
    NumericPolynomialChecks.encodeCombination native.witness145 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 145 [] := by kernel_rfl

theorem native.idealInputsBinding145 :
    CleanExpression.inputs native.expression145 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 145 [] := by kernel_rfl

theorem native.checked145 :
    equal (CleanExpression.polynomial native.placement native.expression145)
        (combination native.relations native.witness145) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression145 native.witness145
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    145 (by decide +kernel) native.idealCodeBinding145 native.idealRelationsBinding native.idealWitnessBinding145

theorem native.preserved145 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression145).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression145 native.placement native.relations native.witness145
    native.checked145 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression146 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨43⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨45⟩))))
    (Airbender.Expression.var ⟨69⟩)

noncomputable def native.witness146 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨178, by decide⟩)]

theorem native.idealCodeBinding146 :
    CleanIdealChecks.encode native.placement native.expression146 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 146 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding146 :
    NumericPolynomialChecks.encodeCombination native.witness146 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 146 [] := by kernel_rfl

theorem native.idealInputsBinding146 :
    CleanExpression.inputs native.expression146 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 146 [] := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
