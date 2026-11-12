module
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part000
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part012
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part013
public import Proven.GKRProtocol.CleanArithmeticNative.KeccakCached.Part053
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

local instance generatedBatch54Instance0 : Field Source.BaseField :=
  ZMod.instField _

local instance generatedBatch54Instance1 : DecidableEq Source.BaseField :=
  ZMod.decidableEq _

theorem native.preserved139 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression139).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression139 native.placement native.relations native.witness139
    native.checked139 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression140 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨39⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨41⟩))))
    (Airbender.Expression.var ⟨68⟩)

noncomputable def native.witness140 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨172, by decide⟩)]

theorem native.idealCodeBinding140 :
    CleanIdealChecks.encode native.placement native.expression140 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 140 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding140 :
    NumericPolynomialChecks.encodeCombination native.witness140 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 140 [] := by kernel_rfl

theorem native.idealInputsBinding140 :
    CleanExpression.inputs native.expression140 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 140 [] := by kernel_rfl

theorem native.checked140 :
    equal (CleanExpression.polynomial native.placement native.expression140)
        (combination native.relations native.witness140) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression140 native.witness140
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    140 (by decide +kernel) native.idealCodeBinding140 native.idealRelationsBinding native.idealWitnessBinding140

theorem native.preserved140 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression140).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression140 native.placement native.relations native.witness140
    native.checked140 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression141 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨40⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨42⟩))))
    (Airbender.Expression.var ⟨68⟩)

noncomputable def native.witness141 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨173, by decide⟩)]

theorem native.idealCodeBinding141 :
    CleanIdealChecks.encode native.placement native.expression141 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 141 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding141 :
    NumericPolynomialChecks.encodeCombination native.witness141 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 141 [] := by kernel_rfl

theorem native.idealInputsBinding141 :
    CleanExpression.inputs native.expression141 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 141 [] := by kernel_rfl

theorem native.checked141 :
    equal (CleanExpression.polynomial native.placement native.expression141)
        (combination native.relations native.witness141) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression141 native.witness141
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    141 (by decide +kernel) native.idealCodeBinding141 native.idealRelationsBinding native.idealWitnessBinding141

theorem native.preserved141 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression141).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression141 native.placement native.relations native.witness141
    native.checked141 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression142 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨43⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨45⟩))))
    (Airbender.Expression.var ⟨68⟩)

noncomputable def native.witness142 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨174, by decide⟩)]

theorem native.idealCodeBinding142 :
    CleanIdealChecks.encode native.placement native.expression142 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).codes.getD 142 (.constant 0) := by kernel_rfl

theorem native.idealWitnessBinding142 :
    NumericPolynomialChecks.encodeCombination native.witness142 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).witnesses.getD 142 [] := by kernel_rfl

theorem native.idealInputsBinding142 :
    CleanExpression.inputs native.expression142 =
      (Airbender.Compiler.CleanIdealNative.KeccakCached.capture).inputs.getD 142 [] := by kernel_rfl

theorem native.checked142 :
    equal (CleanExpression.polynomial native.placement native.expression142)
        (combination native.relations native.witness142) =
      true :=
  CleanIdealChecks.check_sound_at native.placement native.relations native.expression142 native.witness142
    Airbender.Compiler.CleanIdealNative.KeccakCached.capture Airbender.Compiler.CleanIdealNative.KeccakCached.checked
    142 (by decide +kernel) native.idealCodeBinding142 native.idealRelationsBinding native.idealWitnessBinding142

theorem native.preserved142 (base : GKRAddress → Source.BaseField) (data : ProverData Source.BaseField)
    (holds :
      Satisfies native.relations
        (base ∘ (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address)) :
    (native.expression142).eval (native.environment base data) = 0 :=
  CleanExpression.of_combination_at native.expression142 native.placement native.relations native.witness142
    native.checked142 (Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank).address base data holds

noncomputable def native.expression143 : Airbender.Expression Source.BaseField :=
  Airbender.Expression.mul
    (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
      (Airbender.Expression.add
        (Airbender.Expression.add (Airbender.Expression.const (Int.cast (Int.ofNat 0) : Source.BaseField))
          (Airbender.Expression.var ⟨44⟩))
        (Airbender.Expression.mul
          (Airbender.Expression.mul (Airbender.Expression.const (Int.cast (Int.ofNat 1) : Source.BaseField))
            (Airbender.Expression.const (Int.cast (Int.negSucc 0) : Source.BaseField)))
          (Airbender.Expression.var ⟨46⟩))))
    (Airbender.Expression.var ⟨68⟩)

noncomputable def native.witness143 : Combination native.relations :=
  [([((1 : Source.BaseField), [])], ⟨175, by decide⟩)]
end Airbender.Compiler.CleanArithmeticNative.KeccakCached
