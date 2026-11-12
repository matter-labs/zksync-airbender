module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
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

local instance generatedBatch52Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch52Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

noncomputable def native.expression133 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨16⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨58⟩))))
    (Airbender.Expression.var ⟨68⟩)

noncomputable def native.witness133 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨165, by decide⟩)]

theorem native.idealCodeBinding133 :
    CleanIdealChecks.encode native.placement native.expression133 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 133 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding133 :
    NumericPolynomialChecks.encodeCombination native.witness133 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 133 [] := by kernel_rfl

theorem native.idealInputsBinding133 :
    CleanExpression.inputs native.expression133 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 133 [] := by kernel_rfl

theorem native.checked133 :
    equal (CleanExpression.polynomial native.placement native.expression133)
        (combination native.relations native.witness133) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression133 native.witness133
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    133 (by decide +kernel) native.idealCodeBinding133 native.idealRelationsBinding native.idealWitnessBinding133

theorem native.preserved133 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression133).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression133 native.placement native.relations native.witness133
    native.checked133 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression134 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨19⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨61⟩))))
    (Airbender.Expression.var ⟨68⟩)

noncomputable def native.witness134 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨166, by decide⟩)]

theorem native.idealCodeBinding134 :
    CleanIdealChecks.encode native.placement native.expression134 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 134 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding134 :
    NumericPolynomialChecks.encodeCombination native.witness134 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 134 [] := by kernel_rfl

theorem native.idealInputsBinding134 :
    CleanExpression.inputs native.expression134 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 134 [] := by kernel_rfl

theorem native.checked134 :
    equal (CleanExpression.polynomial native.placement native.expression134)
        (combination native.relations native.witness134) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression134 native.witness134
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    134 (by decide +kernel) native.idealCodeBinding134 native.idealRelationsBinding native.idealWitnessBinding134

theorem native.preserved134 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression134).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression134 native.placement native.relations native.witness134
    native.checked134 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression135 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨20⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨62⟩))))
    (Airbender.Expression.var ⟨68⟩)

noncomputable def native.witness135 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨167, by decide⟩)]

theorem native.idealCodeBinding135 :
    CleanIdealChecks.encode native.placement native.expression135 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 135 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding135 :
    NumericPolynomialChecks.encodeCombination native.witness135 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 135 [] := by kernel_rfl

theorem native.idealInputsBinding135 :
    CleanExpression.inputs native.expression135 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 135 [] := by kernel_rfl

theorem native.checked135 :
    equal (CleanExpression.polynomial native.placement native.expression135)
        (combination native.relations native.witness135) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression135 native.witness135
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    135 (by decide +kernel) native.idealCodeBinding135 native.idealRelationsBinding native.idealWitnessBinding135

theorem native.preserved135 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression135).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression135 native.placement native.relations native.witness135
    native.checked135 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression136 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨31⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨33⟩))))
    (Airbender.Expression.var ⟨68⟩)

noncomputable def native.witness136 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨168, by decide⟩)]

theorem native.idealCodeBinding136 :
    CleanIdealChecks.encode native.placement native.expression136 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 136 (.constant 0) := by kernel_rfl
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
