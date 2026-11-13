module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part039
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

local instance generatedBatch40Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch40Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.preserved91 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression91).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression91 native.placement native.relations native.witness91
    native.checked91 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression92 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨39⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨41⟩))))
    (Airbender.Expression.var ⟨63⟩)

noncomputable def native.witness92 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨124, by decide⟩)]

theorem native.idealCodeBinding92 :
    CleanIdealChecks.encode native.placement native.expression92 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 92 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding92 :
    NumericPolynomialChecks.encodeCombination native.witness92 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 92 [] := by kernel_rfl

theorem native.idealInputsBinding92 :
    CleanExpression.inputs native.expression92 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 92 [] := by kernel_rfl

theorem native.checked92 :
    equal (CleanExpression.polynomial native.placement native.expression92)
        (combination native.relations native.witness92) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression92 native.witness92
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 92
    (by decide +kernel) native.idealCodeBinding92 native.idealRelationsBinding native.idealWitnessBinding92

theorem native.preserved92 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression92).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression92 native.placement native.relations native.witness92
    native.checked92 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression93 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨40⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨42⟩))))
    (Airbender.Expression.var ⟨63⟩)

noncomputable def native.witness93 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨125, by decide⟩)]

theorem native.idealCodeBinding93 :
    CleanIdealChecks.encode native.placement native.expression93 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 93 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding93 :
    NumericPolynomialChecks.encodeCombination native.witness93 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 93 [] := by kernel_rfl

theorem native.idealInputsBinding93 :
    CleanExpression.inputs native.expression93 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 93 [] := by kernel_rfl

theorem native.checked93 :
    equal (CleanExpression.polynomial native.placement native.expression93)
        (combination native.relations native.witness93) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression93 native.witness93
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 93
    (by decide +kernel) native.idealCodeBinding93 native.idealRelationsBinding native.idealWitnessBinding93

theorem native.preserved93 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression93).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression93 native.placement native.relations native.witness93
    native.checked93 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression94 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨43⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨45⟩))))
    (Airbender.Expression.var ⟨63⟩)

noncomputable def native.witness94 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨126, by decide⟩)]

theorem native.idealCodeBinding94 :
    CleanIdealChecks.encode native.placement native.expression94 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 94 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding94 :
    NumericPolynomialChecks.encodeCombination native.witness94 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 94 [] := by kernel_rfl

theorem native.idealInputsBinding94 :
    CleanExpression.inputs native.expression94 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 94 [] := by kernel_rfl

theorem native.checked94 :
    equal (CleanExpression.polynomial native.placement native.expression94)
        (combination native.relations native.witness94) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression94 native.witness94
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked 94
    (by decide +kernel) native.idealCodeBinding94 native.idealRelationsBinding native.idealWitnessBinding94

theorem native.preserved94 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression94).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression94 native.placement native.relations native.witness94
    native.checked94 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression95 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨44⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨46⟩))))
    (Airbender.Expression.var ⟨63⟩)

noncomputable def native.witness95 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨127, by decide⟩)]
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
